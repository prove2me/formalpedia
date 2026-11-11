-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:30.342472+00:00
-- url     : https://prove2.me/submissions/747f9533-155d-44df-b47a-1ae6afdbf7f4

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

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
-- module Solutions.Q223_SES.Seshadri_Geometry_AffineLineFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

lemma finite_sections_of_frame {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) : Module.Finite Γ(X,U) Γ(M,U) := by
  let e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := overFrame e
  let j : Over U := Over.mk (𝟙 U)
  let f : Γ(X,U) →ₗ[Γ(X,U)] Γ(M,U) := (e'.inv.val.app (op j)).hom
  have hf : Function.Surjective f := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op j)).mapIso e').inv).surjective
  exact Module.Finite.of_surjective f hf

set_option backward.isDefEq.respectTransparency.types false in
theorem LineBundle.spec_sections_finite {R : CommRingCat.{0}} (L : LineBundle (Spec R)) :
    Module.Finite R ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | Nonempty (L.sheaf.restrict (D r).ι ≅
    structureSheaf (D r).toScheme)}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨⟨MaximalSeshadri.InvertibleLocal.frameOfLE L.sheaf hrU e⟩,hxr⟩⟩
  let M := ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤))
  let (r : t) : Module R Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Module R
      ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op (PrimeSpectrum.basicOpen r.val)))
  let (r : t) : Module Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    (L.sheaf.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Algebra R
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsLocalization.Away r.val Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| IsLocalization.Away r.val
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    IsScalarTower.of_compHom R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val)
  let f (r : t) : M →ₗ[R] Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    ((modulesSpecToSheaf.obj L.sheaf).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing L.sheaf).mp inferInstance
  have (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    finite_sections_of_frame L.sheaf _ r.property.some
  exact Module.Finite.of_localizationSpan' t ht f hfin

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_AffineBundleFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem LineBundle.affine_sections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) Γ(L.sheaf,⊤) := by
  let f := X.isoSpec.inv
  let J := L.restrict f
  let R := Γ(X,⊤)
  let M := (modulesSpecToSheaf.obj J.sheaf).obj.obj (op ⊤)
  let : Module.Finite R M := J.spec_sections_finite
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : M →ₛₗ[σ] Γ(L.sheaf,f ''ᵁ ⊤) := {
    toFun := (L.sheaf.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineLocalizing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    have := hf
    have := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem LineBundle.affine_openSections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) (OpenSections L.sheaf ⊤) := by
  let : Module Γ(X,⊤) Γ(L.sheaf,⊤) := (L.sheaf.val.obj (op ⊤)).isModule
  have := L.affine_sections_finite
  exact Module.Finite.of_surjective (openTopSections L.sheaf).symm.toLinearMap
    (openTopSections L.sheaf).symm.surjective

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictionLocalization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  have : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ChartModuleMap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ChartCoherence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma chartMap_range_coherent (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U) :
    (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
      (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)).range.map
        (chartTop k M W).toLinearMap = (res k M h).range := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨chartTop k M U z, (chartTop_nested k M h z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨_, ⟨(chartTop k M U).symm z,rfl⟩, ?_⟩
    exact (chartTop_nested k M h _).trans
      (congrArg (res k M h) ((chartTop k M U).apply_symm_apply z))

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PencilCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
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
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K]

lemma affine_evaluation_finite {R : Type} [CommRing R] {Y : Scheme}
    (f : R →+* Γ(Y,⊤)) [IsFinite (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    f.Finite := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := g.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.Finite at h
  simpa only [hEq, CommRingCat.hom_ofHom] using h

lemma normalized_evalAway_polyToChart {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (polyToChart i) = eval₂Hom k (fun j : ChartVariables i => a j) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
    change F (chartConstants i r) = k r
    exact RingHom.congr_fun (evalAway_constants k a i hi) r
  · intro j
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
    change F (chartCoordinate i j.val) = a j.val
    have H := evalAway_mk_clear (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (MvPolynomial.X i)) by simpa only [eval₂Hom_X',hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j.val) (by simpa using isHomogeneous_X K j.val)
    simpa only [chartCoordinate, eval₂Hom_X',hi,one_pow,mul_one] using H

theorem finite_sectionsMorphism_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).Finite := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme,⊤) := fun j => coefficient (sectionFrame (s i))
    (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme,⊤))))
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  let chart := Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i)
    (isHomogeneous_X K i) (show 0 < 1 by decide)
  have : IsOpenImmersion chart := V.map_prop i
  have H : IsPullback g U.ι chart (sectionsMorphism k s hs) := by
    apply IsOpenImmersion.isPullback
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · have hrange : chart.opensRange =
          Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X i) :=
        Proj.opensRange_awayι _ _ (isHomogeneous_X K i) (show 0 < 1 by decide)
      rw [hrange, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsFinite g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨isAffine_of_isAffineHom g, ?_⟩
  have hf := (@affine_evaluation_finite _ _ U.toScheme f hg).comp (RingHom.Finite.of_surjective
    (polyToChart (R := K) i) (polynomialChartEquiv (R := K) i).symm.surjective)
  rwa [normalized_evalAway_polyToChart k' a i hi] at hf

theorem finite_pencil_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : Bool → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : Bool) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i))))).Finite := by
  obtain ⟨hA,hf⟩ := finite_sectionsMorphism_chart k s hs i
  refine ⟨hA, ?_⟩
  have h := hf.comp (RingHom.Finite.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.surjective)
  have he : (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).comp
      (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom =
      Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.uniqueAlgEquiv]
    · have hd : (default : ChartVariables i).val = !i :=
        congrArg Subtype.val (Subsingleton.elim (default : ChartVariables i)
          ⟨!i, by cases i <;> decide⟩)
      simpa [MvPolynomial.uniqueAlgEquiv] using congrArg
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) hd
  rwa [he] at h
end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PencilOverlap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.sectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}} {M : X.Modules}

lemma pencil_overlap_basic (s : Bool → (O X ⟶ M)) (i : Bool) :
    (SectionOpens.isoOpen (s i)).ι ⁻¹ᵁ SectionOpens.isoOpen (s (!i)) =
      (SectionOpens.isoOpen (s i)).toScheme.basicOpen
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) :=
  preimage_isoOpen _ _ _

lemma pencil_overlap_reciprocal (s : Bool → (O X ⟶ M)) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    let a := X.homOfLE (show U ⊓ V ≤ U from inf_le_left)
    let b := X.homOfLE (show U ⊓ V ≤ V from inf_le_right)
    a.appTop (coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))) *
      b.appTop (coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))) = 1 := by
  intro U V a b
  obtain ⟨c,hc⟩ := overlap_coefficients U.ι V.ι a b
    (by simp only [a,b, Scheme.homOfLE_ι])
    (sectionFrame (s false)) (sectionFrame (s true))
  have h0 := hc (s false)
  have h1 := hc (s true)
  have hv : b.appTop (coefficient (sectionFrame (s true))
      (restrictSection V.ι (s false))) = c := by
    simpa only [U, sectionFrame_normalized, map_one, mul_one] using h0
  rw [hv, mul_comm]
  simpa only [V, sectionFrame_normalized, map_one] using h1.symm

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentLattices
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

variable {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

lemma mem_boundedBelow (b : Basis ι K[T;T⁻¹] M) (l : ℤ) (x : M) :
    x ∈ boundedBelow b l ↔ ∀ i z, z < l → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedBelow, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Ici, not_le]

lemma mem_boundedAbove (b : Basis ι K[T;T⁻¹] M) (u : ℤ) (x : M) :
    x ∈ boundedAbove b u ↔ ∀ i z, u < z → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedAbove, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Iic, not_le]

lemma coeff_T_mul (p : K[T;T⁻¹]) (n z : ℤ) :
    (T n * p).coeff z = p.coeff (z-n) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

lemma below_shift (b : Basis ι K[T;T⁻¹] M) (l : ℤ) {x : M}
    (hx : x ∈ boundedBelow b l) (n : ℕ) :
    (T (n : ℤ) : K[T;T⁻¹]) • x ∈ boundedBelow b l := by
  rw [mem_boundedBelow] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

lemma above_shift (b : Basis ι K[T;T⁻¹] M) (u : ℤ) {x : M}
    (hx : x ∈ boundedAbove b u) (n : ℕ) :
    (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ boundedAbove b u := by
  rw [mem_boundedAbove] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

theorem band_finite [Fintype ι] (b : Basis ι K[T;T⁻¹] M) (l u : ℤ) :
    Module.Finite K ↥(boundedBelow b l ⊓ boundedAbove b u) := by
  classical
  let W := boundedBelow b l ⊓ boundedAbove b u
  let J := ι × ↥(Finset.Icc l u)
  let φ : W →ₗ[K] (J → K) := LinearMap.pi (fun j =>
    (Finsupp.lapply j.2.val).comp ((AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap.comp
      ((((Finsupp.lapply j.1).comp b.repr.toLinearMap).restrictScalars K).comp W.subtype)))
  apply Module.Finite.of_injective φ
  intro x y hxy
  apply Subtype.ext
  apply b.repr.injective
  ext i z
  by_cases hzL : z < l
  · rw [(mem_boundedBelow b l x.val).mp x.property.1 i z hzL,
      (mem_boundedBelow b l y.val).mp y.property.1 i z hzL]
  · by_cases hzU : u < z
    · rw [(mem_boundedAbove b u x.val).mp x.property.2 i z hzU,
        (mem_boundedAbove b u y.val).mp y.property.2 i z hzU]
    · exact congrFun hxy (i,⟨z,Finset.mem_Icc.mpr (by omega)⟩)

lemma finite_generators_bounded [Fintype ι] {κ : Type*} [Fintype κ]
    (b : Basis ι K[T;T⁻¹] M) (s : κ → M) :
    ∃ l u : ℤ, ∀ j, s j ∈ boundedBelow b l ∧ s j ∈ boundedAbove b u := by
  classical
  let S : Set ℤ := ⋃ i, ⋃ j, (↑((b.repr (s j)) i).coeff.support : Set ℤ)
  have hS : S.Finite := Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    Finset.finite_toSet _
  obtain ⟨l,hl⟩ := hS.bddBelow
  obtain ⟨u,hu⟩ := hS.bddAbove
  refine ⟨l,u,fun j => ⟨?_,?_⟩⟩
  · rw [mem_boundedBelow]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hl hm)
  · rw [mem_boundedAbove]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hu hm)

theorem intersection_finite [Module.Finite K[T;T⁻¹] M]
    [Module.IsTorsionFree K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let b := Module.Free.chooseBasis K[T;T⁻¹] M
  obtain ⟨l,_,hs⟩ := finite_generators_bounded b s
  obtain ⟨_,u,ht⟩ := finite_generators_bounded b t
  have hbelow : A ≤ boundedBelow b l := hA.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact below_shift b l (hs j).1 n))
  have habove : B ≤ boundedAbove b u := hB.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact above_shift b u (ht j).2 n))
  let := band_finite b l u
  exact Module.Finite.of_injective (Submodule.inclusion (inf_le_inf hbelow habove))
    (Submodule.inclusion_injective _)

end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentTorsion
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

lemma quotient_finite (a : K[T;T⁻¹]) (ha : a ≠ 0) :
    Module.Finite K (K[T;T⁻¹] ⧸ Ideal.span {a}) := by
  let : IsPrincipalIdealRing K[T;T⁻¹] := ⟨fun ideal => by
    rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : K[X])) K[T;T⁻¹] ideal]
    exact (IsPrincipalIdealRing.principal (ideal.under K[X])).map_ringHom _⟩
  have hlen := isFiniteLength_quotient_span_singleton K[T;T⁻¹]
    (mem_nonZeroDivisors_of_ne_zero ha)
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  let : IsArtinianRing (K[T;T⁻¹] ⧸ Ideal.span {a}) :=
    isArtinian_of_tower K[T;T⁻¹] inferInstance
  exact Module.finite_of_isArtinianRing K _

theorem torsion_finite {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M] [Module.Finite K[T;T⁻¹] M]
    (hM : Module.IsTorsion K[T;T⁻¹] M) : Module.Finite K M := by
  obtain ⟨a,ha,hn⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hkill : Module.IsTorsionBy K[T;T⁻¹] M a := fun x =>
    Submodule.mem_annihilator.mp ha x trivial
  let hset : Module.IsTorsionBySet K[T;T⁻¹] M (Ideal.span {a}) :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr hkill
  let := hset.module
  let : IsScalarTower K[T;T⁻¹] (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : IsScalarTower K (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : Module.Finite (K[T;T⁻¹] ⧸ Ideal.span {a}) M :=
    Module.Finite.of_restrictScalars_finite K[T;T⁻¹] _ M
  let := quotient_finite a (nonZeroDivisors.ne_zero hn)
  exact Module.Finite.trans (K[T;T⁻¹] ⧸ Ideal.span {a}) M
end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

theorem intersection_finite_general [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let D := Submodule.torsion K[T;T⁻¹] M
  let q := D.mkQ.restrictScalars K
  let : Module.Finite K D := torsion_finite Submodule.torsion_isTorsion
  have ha : A.map q ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • q (s j.1))) := by
    apply (Submodule.map_mono hA).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  have hb : B.map q ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • q (t j.1))) := by
    apply (Submodule.map_mono hB).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  let := intersection_finite (A.map q) (B.map q) (fun i => q (s i))
    (fun i => q (t i)) ha hb
  let f : ↥(A ⊓ B) →ₗ[K] ↥(A.map q ⊓ B.map q) :=
    (q.comp (A ⊓ B).subtype).codRestrict _ (fun x =>
      ⟨Submodule.mem_map.mpr ⟨x.val,x.property.1,rfl⟩,
        Submodule.mem_map.mpr ⟨x.val,x.property.2,rfl⟩⟩)
  let g : f.ker →ₗ[K] D :=
    (((A ⊓ B).subtype.comp f.ker.subtype).codRestrict (D.restrictScalars K)
      (fun x => by
        have h : q x.val.val = 0 := congrArg Subtype.val x.property
        exact (Submodule.Quotient.mk_eq_zero D).mp h))
  let : Module.Finite K f.ker := Module.Finite.of_injective g (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D => (z : M)) h)
  let : Module.Finite K (↥(A ⊓ B) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.ker
end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PolynomialLattices
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K N Q : Type*} [Field K] [AddCommGroup N] [AddCommGroup Q]
  [Module K N] [Module K Q] [Module K[X] N] [IsScalarTower K K[X] N]
  [Module K[T;T⁻¹] Q] [IsScalarTower K K[T;T⁻¹] Q]

omit [IsScalarTower K K[T;T⁻¹] Q] in
lemma range_le_lattice {ι : Type*} [Fintype ι] (s : ι → N)
    (hs : Submodule.span K[X] (Set.range s) = ⊤) (g : N →ₗ[K] Q) (d : ℤ)
    (hpow : ∀ (n : ℕ) (x : N), g ((Polynomial.X : K[X])^n • x) =
      (T (d*n) : K[T;T⁻¹]) • g x) :
    g.range ≤ Submodule.span K (Set.range (fun j : ι × ℕ =>
      (T (d*j.2) : K[T;T⁻¹]) • g (s j.1))) := by
  classical
  rintro _ ⟨x,rfl⟩
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    (show x ∈ Submodule.span K[X] (Set.range s) from hs ▸ trivial)
  rw [← hf, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [← Polynomial.sum_C_mul_X_pow_eq (f i), Polynomial.sum, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul, map_smul, hpow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,n),rfl⟩)

theorem range_intersection_finite [Module.Finite K[X] N]
    {P : Type*} [AddCommGroup P] [Module K P] [Module K[X] P]
    [IsScalarTower K K[X] P] [Module.Finite K[X] P]
    [Module.Finite K[T;T⁻¹] Q]
    (f : N →ₗ[K] Q) (g : P →ₗ[K] Q)
    (hf : ∀ x, f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x)
    (hg : ∀ x, g ((Polynomial.X : K[X]) • x) = (T (-1) : K[T;T⁻¹]) • g x) :
    Module.Finite K ↥(f.range ⊓ g.range) := by
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[X]) (M := N)
  obtain ⟨m,t,ht⟩ := Module.Finite.exists_fin (R := K[X]) (M := P)
  have hp (j : ℕ) (x : N) : f ((Polynomial.X : K[X])^j • x) =
      (T (1*(j : ℤ)) : K[T;T⁻¹]) • f x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  have hn (j : ℕ) (x : P) : g ((Polynomial.X : K[X])^j • x) =
      (T ((-1)*(j : ℤ)) : K[T;T⁻¹]) • g x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hg, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  apply intersection_finite_general f.range g.range (fun i => f (s i)) (fun i => g (t i))
  · simpa only [one_mul] using range_le_lattice s hs f 1 hp
  · simpa only [neg_one_mul] using range_le_lattice t ht g (-1) hn
end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentH0
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.LaurentCech
noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

theorem intersection_finite [Module.Finite K[X] N] [Module.Finite K[X] P]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y) :
    Module.Finite K ↥((f.restrictScalars K).range ⊓ g.range) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentLattices.range_intersection_finite (f.restrictScalars K) g
  · intro x
    change f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x
    rw [map_smul, pos1]
  · intro y
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
end
end MaximalSeshadri.LaurentCech
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_PolynomialSections
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [CommRing K] {X : Scheme.{0}}

theorem polynomialTower (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    letI := polynomialModule k t M U
    IsScalarTower K K[X] (Sections k M U) := by
  let := polynomialModule k t M U
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Polynomial.eval₂RingHom k t) (Polynomial.C r) • (m : OpenSections M U) =
    k r • (m : OpenSections M U)
  simp

theorem polynomial_finite [IsAffine X] (k : K →+* Γ(X,⊤))
    (t : Γ(X,⊤)) (L : LineBundle X)
    (h : (Polynomial.eval₂RingHom k t).Finite) :
    letI := polynomialModule k t L.sheaf ⊤
    Module.Finite K[X] (Sections k L.sheaf ⊤) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom k t).toAlgebra
  let : Module.Finite K[X] Γ(X,⊤) := h
  let := polynomialModule k t L.sheaf ⊤
  let : Module.Finite Γ(X,⊤) (Sections k L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower K[X] Γ(X,⊤) (Sections k L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.trans Γ(X,⊤) (Sections k L.sheaf ⊤)

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ChartPolynomial
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

theorem chartPolynomialMap_localize [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    IsLocalizedModule.Away (Polynomial.X : K[X])
      (chartPolynomialMap kX kY f hk M e t) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom kX t).toAlgebra
  let := polynomialModule kX t M ⊤
  let := polynomialModule kY (f.appTop t) N ⊤
  let : Module Γ(X,⊤) (Sections kY N ⊤) :=
    Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kX M ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kY N ⊤) :=
    .of_algebraMap_smul (fun p m => by
      change f.appTop ((Polynomial.eval₂RingHom kX t) p) • (m : OpenSections N ⊤) =
        (Polynomial.eval₂RingHom kY (f.appTop t)) p • (m : OpenSections N ⊤)
      rw [eval_transport kX kY f hk])
  let F : Sections kX M ⊤ →ₗ[Γ(X,⊤)] Sections kY N ⊤ := chartModuleMap M f e
  have he : algebraMap K[X] Γ(X,⊤) Polynomial.X = t := by
    change (Polynomial.eval₂RingHom kX t) Polynomial.X = t
    simp
  let : IsLocalizedModule (.powers (algebraMap K[X] Γ(X,⊤) Polynomial.X)) F := by
    rw [he]
    exact chartModuleMap_localize M f e t ht
  have h := IsLocalizedModule.restrictScalars_powers (Polynomial.X : K[X]) F
  exact h
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_TwoChartIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_intersection_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (_hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (hv : (Polynomial.eval₂RingHom kV v).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K ↥((chartMap kU kW a hka L.sheaf e).range ⊓
        (chartMap kV kW b hkb P.sheaf d).range) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let : Module.Finite K[X] (Sections kV P.sheaf ⊤) := polynomial_finite kV v P hv
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  exact LaurentCech.intersection_finite F G hInv
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_PencilIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_intersection (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K ↥(twoBaseIntersection k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k (show W ≤ U from inf_le_left))
    (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k (show W ≤ V from inf_le_right))
    (L.restrict V.ι).sheaf d
  let : Module.Finite K ↥(F.range ⊓ G.range) :=
    two_chart_intersection_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu hv
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊓ G.range).map E.toLinearMap = twoBaseIntersection k L.sheaf U V := by
    rw [Submodule.map_inf E.toLinearMap E.injective]
    change F.range.map E.toLinearMap ⊓ G.range.map E.toLinearMap =
      (res k L.sheaf (show W ≤ U from inf_le_left)).range ⊓
        (res k L.sheaf (show W ≤ V from inf_le_right)).range
    exact congrArg₂ (· ⊓ ·)
      (chartMap_range_coherent k L.sheaf (show W ≤ U from inf_le_left))
      (chartMap_range_coherent k L.sheaf (show W ≤ V from inf_le_right))
  let : Module.Finite K ↥((F.range ⊓ G.range).map E.toLinearMap) :=
    Module.Finite.equiv (E.submoduleMap (F.range ⊓ G.range))
  rw [← he]
  infer_instance
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveH0Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.globalIntersection_injective [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) [Nonempty (U ⊓ V : X.Opens)] :
    Function.Injective (globalIntersection k L U V) := by
  intro a b h
  exact L.restriction_injective (homOfLE (show U ⊓ V ≤ ⊤ from le_top))
    (congrArg Subtype.val h)

theorem finite_pencil_H0_finite [IsIntegral X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) k
    Module.Finite K (cohomology L.sheaf 0) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  have hneU : (U : Set X).Nonempty := by
    by_contra h
    have he : U = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, bot_sup_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hV
    exact hn (.of_isIso X.topIso.inv)
  have hneV : (V : Set X).Nonempty := by
    by_contra h
    have he : V = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, sup_bot_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hU
    exact hn (.of_isIso X.topIso.inv)
  obtain ⟨x,hxU,hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hneU hneV
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x,hxU,hxV⟩⟩
  let := finite_pencil_intersection k s hs L
  let : Module.Finite K (Sections k L.sheaf ⊤) := Module.Finite.of_injective
    (globalIntersection k L U V) (globalIntersection_injective k L U V)
  let := Module.compHom (cohomology L.sheaf 0) k
  exact Module.Finite.equiv (cohomologyZero k L.sheaf).symm

theorem projective_curve_H0_finite {σ : Type} [Fintype σ] [Infinite K]
    [IsIntegral X] [IsNoetherian X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf 0) := by
  obtain ⟨t,ht,hf⟩ := projective_curve_finite_pencil p hd s hs
  let := hf
  apply finite_pencil_H0_finite _ t ht ?_ L
  intro h
  let : IsAffine X := h
  have hh := proper_affine_dimension_zero p
  rw [hd] at hh
  norm_num at hh
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentTails
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.LaurentTails
noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module K[T;T⁻¹] M]

lemma positive_tail (A : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A) {x : M} (hx : x ∈ A) :
    ∀ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, T_add, mul_smul]
      using hA _ ih

lemma negative_tail (B : Submodule K M)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B) {x : M} (hx : x ∈ B) :
    ∀ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have he : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    simpa only [he, T_add, mul_smul] using hB _ ih

variable [IsScalarTower K K[T;T⁻¹] M]

theorem quotient_finite [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B)
    (locA : ∀ x : M, ∃ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B) :
    Module.Finite K (M ⧸ (A ⊔ B)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[T;T⁻¹]) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  let q := (A ⊔ B).mkQ
  let J := (i : Fin n) × ↥(Finset.Icc (-(b i : ℤ)) (a i : ℤ))
  let g : J → M ⧸ (A ⊔ B) := fun v => q ((T v.2.val : K[T;T⁻¹]) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ) : q ((T z : K[T;T⁻¹]) • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z
    · have he : z = ((z - a i).toNat : ℤ) + a i := by omega
      have hm : (T z : K[T;T⁻¹]) • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact positive_tail A hA (ha i) _
      have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
        (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show A ≤ A ⊔ B from le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : z ≤ -(b i : ℤ)
      · have he : z = -((-(b i : ℤ) - z).toNat : ℤ) + -(b i : ℤ) := by omega
        have hm : (T z : K[T;T⁻¹]) • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact negative_tail B hB (hb i) _
        have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
          (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show B ≤ A ⊔ B from le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · exact Submodule.subset_span ⟨⟨i,⟨z,Finset.mem_Icc.mpr (by omega)⟩⟩,rfl⟩
  have scalar_monomial (i : Fin n) (p : K[T;T⁻¹]) : q (p • s i) ∈ W := by
    induction p using LaurentPolynomial.induction_on' with
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | C_mul_T z c =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul, map_smul]
      exact W.smul_mem c (monomial i z)
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m,rfl⟩ := (A ⊔ B).mkQ_surjective x
    have hm : m ∈ Submodule.span K[T;T⁻¹] (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : K[T;T⁻¹], q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro scalar; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end
end MaximalSeshadri.LaurentTails
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.LaurentCech
noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] Q]

theorem cokernel_finite [Module.Finite K[X] N]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y)
    (opposite_denominators : ∀ x : Q, ∃ n : ℕ, ∃ y : P,
      ((Polynomial.X : K[X])^n) • g y = x) :
    Module.Finite K (Q ⧸ ((f.restrictScalars K).range ⊔ g.range)) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentTails.quotient_finite (A := (f.restrictScalars K).range) (B := g.range)
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    change f ((Polynomial.X : K[X]) • y) = (T 1 : K[T;T⁻¹]) • f y
    rw [map_smul, pos1]
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
  · intro x
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away (Polynomial.X : K[X]) f).surj _ _ x
    refine ⟨n, y, ?_⟩
    change f y = (T (n : ℤ) : K[T;T⁻¹]) • x
    rw [pos]
    exact hy.symm
  · intro x
    obtain ⟨n,y,hy⟩ := opposite_denominators x
    refine ⟨n,y,?_⟩
    rw [← hy, ← pos n, cancel n]
end
end MaximalSeshadri.LaurentCech
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_TwoChartFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_cokernel_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K (Sections kW N ⊤ ⧸
      ((chartMap kU kW a hka L.sheaf e).range ⊔
        (chartMap kV kW b hkb P.sheaf d).range)) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  have := polynomialTower kU u L.sheaf ⊤
  have := polynomialTower kV v P.sheaf ⊤
  have := polynomialTower kW (a.appTop u) N ⊤
  have : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  have : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  have hDen (x : OpenSections N ⊤) : ∃ n : ℕ, ∃ y : Sections kV P.sheaf ⊤,
      (Polynomial.X : K[X])^n • G y = x := by
    let : Module Γ(V,⊤) (OpenSections N ⊤) :=
      Module.compHom (OpenSections N ⊤) b.appTop.hom
    let G' := chartModuleMap P.sheaf b d
    have : IsLocalizedModule.Away v G' := chartModuleMap_localize P.sheaf b d v hb
    obtain ⟨n,y,hy⟩ := IsLocalizedModule.Away.surj G' v x
    refine ⟨n,y,?_⟩
    change (Polynomial.eval₂RingHom kW (a.appTop u)) (Polynomial.X^n) • G y = x
    simp only [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change b.appTop (v^n) • (x : OpenSections N ⊤) = G' y at hy
    change (a.appTop u)^n • (G' y : OpenSections N ⊤) = x
    rw [← hy, map_pow, ← mul_smul, ← mul_pow, huv, one_pow, one_smul]
  exact LaurentCech.cokernel_finite F G hInv hDen
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PencilCokernel
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_cokernel (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K (Sections k L.sheaf (U ⊓ V) ⧸ twoBaseImage k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K (Sections kW (L.sheaf.restrict W.ι) ⊤ ⧸ (F.range ⊔ G.range)) :=
    two_chart_cokernel_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊔ G.range).map E.toLinearMap = twoBaseImage k L.sheaf U V := by
    rw [Submodule.map_sup]
    exact congrArg₂ (· ⊔ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let q := Submodule.Quotient.equiv (F.range ⊔ G.range)
    (twoBaseImage k L.sheaf U V) E he
  exact Module.Finite.of_surjective q.toLinearMap q.surjective
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CurveH1Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} [IsNoetherian X]

theorem finite_pencil_H1_finite (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    Module.Finite K (cohomology L.sheaf 1) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  let := Module.compHom (cohomology L.sheaf 1) k
  let := finite_pencil_cokernel k s hs L
  let e := twoBaseCohomologyOne k L.sheaf U V hU hV hc
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

theorem projective_curve_H1_finite {σ : Type} [Fintype σ] [Infinite K]
    [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf 1) := by
  obtain ⟨t,ht,hf⟩ := projective_curve_finite_pencil p hd s hs
  let := hf
  exact finite_pencil_H1_finite _ t ht L
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ProjectiveCurveCohomology
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem projective_curve_cohomology_finite_s01_oai
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf n) := by
  cases n with
  | zero => exact projective_curve_H0_finite p hd s hs L
  | succ n => cases n with
    | zero => exact projective_curve_H1_finite p hd s hs L
    | succ n =>
      let := Module.compHom (cohomology L.sheaf (n+2))
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      have : L.sheaf.IsQuasicoherent := L.quasicoherent
      have : Subsingleton (cohomology L.sheaf (n+2)) := ⟨fun x y =>
        (projective_curve_ext_zero p hd s hs L.sheaf n x).trans
          (projective_curve_ext_zero p hd s hs L.sheaf n y).symm⟩
      infer_instance
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01_oai := @OAI.MaximalSeshadri.Geometry.projective_curve_cohomology_finite_s01_oai
