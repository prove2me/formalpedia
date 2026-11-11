-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:39.973664+00:00
-- url     : https://prove2.me/submissions/2e42da7c-bf15-415e-9b16-12ca4c8a35dc

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_power_section_embedding_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_local_powerSection_coefficient_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_dimension_le_one_s01

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_SectionOpens
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.sectionOpen_power (L : LineBundle X) (s : GlobalSections X L.sheaf)
    {n : ℕ} (hn : 0 < n) :
    sectionOpen X (powerSection s n) = sectionOpen X s := by
  have hlocal (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
      U.ι ⁻¹ᵁ sectionOpen X (powerSection s n) = U.ι ⁻¹ᵁ sectionOpen X s := by
    change U.ι ⁻¹ᵁ SectionOpens.isoOpen (powerSection s n) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen s
    calc
      _ = U.toScheme.basicOpen (coefficient (localPowerFrame U e n)
          (restrictSection U.ι (powerSection s n))) :=
        preimage_isoOpen (powerSection s n) U.ι (localPowerFrame U e n)
      _ = U.toScheme.basicOpen (endValue (powerRestrictionUnit U n).hom *
          coefficient e (restrictSection U.ι s) ^ n) :=
        congrArg U.toScheme.basicOpen (local_powerSection_coefficient_s01 U e s n)
      _ = U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) := by
        rw [Scheme.basicOpen_mul,
          Scheme.basicOpen_of_isUnit _ (local_powerSection_coefficient_unit U n),
          top_inf_eq]
        exact U.toScheme.basicOpen_pow (coefficient e (restrictSection U.ι s)) hn
      _ = _ := (preimage_isoOpen s U.ι e).symm
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have h := congrArg (fun V : U.toScheme.Opens => (⟨x, hxU⟩ : U.toScheme) ∈ V) (hlocal U e)
  exact Iff.of_eq h

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
-- module Solutions.Q223_SES.Seshadri_Sheaves_PowerExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.sectionsMorphism_proper _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
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
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι κ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem framedSectionsMorphism_eq (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)
    (V : κ → X.Opens) (hd : (⨆ i, V i) = ⊤)
    (d : ∀ i, M.restrict (V i).ι ≅ O (V i).toScheme) (b : κ → σ)
    (hnorm' : ∀ i, coefficient (d i) (restrictSection (V i).ι (s (b i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm =
      framedSectionsMorphism k s V hd d b hnorm' := by
  let W : ι ⊕ κ → X.Opens := Sum.elim U V
  have hw : (⨆ i, W i) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact le_iSup W (Sum.inl i)
  let E : ∀ i, M.restrict (W i).ι ≅ O (W i).toScheme :=
    fun i => match i with | Sum.inl j => e j | Sum.inr j => d j
  let A : ι ⊕ κ → σ := Sum.elim a b
  have hN : ∀ i, coefficient (E i) (restrictSection (W i).ι (s (A i))) = 1 := by
    rintro (i | i)
    · exact hnorm i
    · exact hnorm' i
  let F := framedSectionsMorphism k s W hw E A hN
  have hleft : framedSectionsMorphism k s U hc e a hnorm = F := by
    apply (X.openCoverOfIsOpenCover U hc).hom_ext
    intro i
    change ι at i
    change (U i).ι ≫ _ = (U i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inl i)).symm
  have hright : framedSectionsMorphism k s V hd d b hnorm' = F := by
    apply (X.openCoverOfIsOpenCover V hd).hom_ext
    intro i
    change κ at i
    change (V i).ι ≫ _ = (V i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inr i)).symm
  exact hleft.trans hright.symm

lemma framedSectionsMorphism_eq_sectionsMorphism (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm = sectionsMorphism k s hs :=
  framedSectionsMorphism_eq k s U hc e a hnorm
    (fun i => SectionOpens.isoOpen (s i)) hs (fun i => sectionFrame (s i)) id
    (fun i => sectionFrame_normalized (s i))

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}} {M N : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_postcomp (f : M ≅ N) (φ : X.Opens)
    (e : M.restrict φ.ι ≅ O φ.toScheme) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctor φ.ι).mapIso f.symm ≪≫ e)
      (restrictSection φ.ι (s ≫ f.hom)) = coefficient e (restrictSection φ.ι s) := by
  change endValue
    (((Scheme.Modules.restrictUnitIso φ.ι).inv ≫
      (Scheme.Modules.restrictFunctor φ.ι).map (s ≫ f.hom)) ≫
      (Scheme.Modules.restrictFunctor φ.ι).map f.inv ≫ e.hom) = _
  erw [Functor.map_comp]
  erw [Category.assoc, Category.assoc,
    ((Scheme.Modules.restrictFunctor φ.ι).mapIso f).hom_inv_id_assoc]
  exact congrArg endValue (Category.assoc _ _ _).symm

theorem sectionsMorphism_transport (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : M ≅ N) (ht : (⨆ i, SectionOpens.isoOpen (s i ≫ f.hom)) = ⊤) :
    sectionsMorphism k (fun i => s i ≫ f.hom) ht = sectionsMorphism k s hs := by
  let U (i : σ) := SectionOpens.isoOpen (s i)
  let e (i : σ) := (Scheme.Modules.restrictFunctor (U i).ι).mapIso f.symm ≪≫ sectionFrame (s i)
  have he (i j : σ) : coefficient (e i) (restrictSection (U i).ι (s j ≫ f.hom)) =
      coefficient (sectionFrame (s i)) (restrictSection (U i).ι (s j)) :=
    coefficient_postcomp f (U i) (sectionFrame (s i)) (s j)
  have hn (i : σ) : coefficient (e i) (restrictSection (U i).ι (s i ≫ f.hom)) = 1 := by
    rw [he]
    exact sectionFrame_normalized (s i)
  rw [← framedSectionsMorphism_eq_sectionsMorphism k (fun i => s i ≫ f.hom) ht U hs e id hn]
  apply (X.openCoverOfIsOpenCover U hs).hom_ext
  intro i
  change σ at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [framedSectionsMorphism_local, sectionsMorphism_local]
  congr 1
  funext j
  exact he i j

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_AmpleEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

theorem LineBundle.ample_projective_sections [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  obtain ⟨d, hd, l, s, hc, ha, hn⟩ := L.ample_common_degree_cover hL
  obtain ⟨n, hn', σ, hσ, t, ht, he⟩ := (L.pow d).power_section_embedding_s01 p s hc ha hn
  let e := linePowerMul L d n
  let T : σ → GlobalSections X (modulePow X L.sheaf (d*n)) := fun i => t i ≫ e.hom
  have hT : (⨆ i, SectionOpens.isoOpen (T i)) = ⊤ := by
    calc
      (⨆ i, SectionOpens.isoOpen (T i)) = ⨆ i, SectionOpens.isoOpen (t i) :=
        iSup_congr fun i => SectionOpens.isoOpen_postcomp (t i) e
      _ = ⊤ := ht
  refine ⟨d*n, Nat.mul_pos hd hn', σ, hσ, T, hT, ?_⟩
  dsimp only [T]
  erw [sectionsMorphism_transport _ t ht e hT]
  exact he

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Projective

theorem Surface.ample_embedding (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections S.scheme (modulePow S.scheme L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) t ht) :=
  L.ample_projective_sections S.structureMap hL

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_AmpleCurveDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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

lemma section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x,hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  rw [restrictSection_zero,coefficient_zero (X := U.toScheme) e,
    Scheme.basicOpen_zero] at hm
  exact hm

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SurfaceAffineCover
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
open TopologicalSpace Set

theorem exists_finite_test_set_of_dimension_one
    (X : Type*) [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) :
    ∃ T : Set X, T.Finite ∧ ∀ U : Set X, IsOpen U → T ⊆ U → Uᶜ.Finite := by
  classical
  obtain ⟨F,hF,hFc,hFi,hFcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ : IsClosed (univ : Set X))
  let x (C : F) : X := (hFi C.1 C.2).nonempty.choose
  have hx (C : F) : x C ∈ C.1 := (hFi C.1 C.2).nonempty.choose_spec
  let : Finite F := hF.to_subtype
  refine ⟨Set.range x, Set.finite_range x, ?_⟩
  intro U hU hTU
  have hpiece (C : F) : (C.1 ∩ Uᶜ).Finite := by
    let : IrreducibleSpace C.1 := Subtype.irreducibleSpace (hFi C.1 C.2)
    have hdC : topologicalKrullDim C.1 ≤ 1 :=
      (topologicalKrullDim_subspace_le X C.1).trans hd
    have hz : ((Subtype.val : C.1 → X) ⁻¹' Uᶜ).Finite := by
      apply proper_closed_finite_of_dimension_one hdC
        (hU.isClosed_compl.preimage continuous_subtype_val)
      intro he
      have hm : (⟨x C,hx C⟩ : C.1) ∈ (Subtype.val : C.1 → X) ⁻¹' Uᶜ := by
        rw [he]; trivial
      exact hm (hTU (Set.mem_range_self C))
    have he : C.1 ∩ Uᶜ = Subtype.val '' ((Subtype.val : C.1 → X) ⁻¹' Uᶜ) := by
      ext y
      constructor
      · intro hy
        exact ⟨⟨y,hy.1⟩,hy.2,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y.2,hy⟩
    rw [he]
    exact hz.image _
  have he : Uᶜ = ⋃ C : F, C.1 ∩ Uᶜ := by
    ext y
    constructor
    · intro hy
      have hyF : y ∈ ⋃₀ F := hFcover ▸ Set.mem_univ y
      obtain ⟨C,hC,hyC⟩ := hyF
      exact Set.mem_iUnion.mpr ⟨⟨C,hC⟩,hyC,hy⟩
    · intro hy
      obtain ⟨C,hyC⟩ := Set.mem_iUnion.mp hy
      exact hyC.2
  rw [he]
  exact Set.finite_iUnion hpiece

end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

omit [Infinite K] in
lemma sectionIdeal_support_eq {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) :
    ((sectionIdeal k s hs v).support : Set X) =
      (SectionOpens.isoOpen (sectionCombination k s v) : Set X)ᶜ := by
  rw [sectionIdeal, Scheme.IdealSheafData.support_comap]
  simp only [ambientHyperplane, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_preimage, Opens.coe_compl]
  rw [← sectionsMorphism_hyperplane k s hs]
  rfl

theorem surface_three_sections [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ v : Fin 3 → (σ → K),
      (⨆ i, SectionOpens.isoOpen (sectionCombination (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s (v i))) = ⊤ := by
  classical
  let k : K →+* Γ(X,⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨v₀,hv₀⟩ := exists_section_avoiding k s hs (fun _ : Unit => x)
  have hne : sectionCombination k s v₀ ≠ 0 :=
    section_ne_zero_of_mem_isoOpen L _ x (hv₀ ())
  let I : X.IdealSheafData := sectionIdeal k s hs v₀
  let U₀ := SectionOpens.isoOpen (sectionCombination k s v₀)
  have hsupport : (I.support : Set X) = (U₀ : Set X)ᶜ := sectionIdeal_support_eq k s hs v₀
  have hbase : sectionsMorphism k s hs ≫ projectiveToSpec = p := by
    change _ ≫ projectiveBase = p
    rw [sectionsMorphism_over, toSpec_scalarMap]
  have hd : topologicalKrullDim I.subscheme ≤ 1 :=
    sectionIdeal_dimension_le_one_s01 p (sectionsMorphism k s hs) hbase L k s hs v₀ hne
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : IsNoetherian I.subscheme := {}
  obtain ⟨T,hT,hdetect⟩ := exists_finite_test_set_of_dimension_one I.subscheme hd
  let : Finite T := hT.to_subtype
  obtain ⟨v₁,hv₁⟩ := exists_section_avoiding k s hs (fun z : T => I.subschemeι z.1)
  let U₁ := SectionOpens.isoOpen (sectionCombination k s v₁)
  have hfin : ((I.subschemeι ⁻¹ᵁ U₁ : I.subscheme.Opens) : Set I.subscheme)ᶜ.Finite := by
    apply hdetect _ (I.subschemeι ⁻¹ᵁ U₁).isOpen
    intro z hz
    exact hv₁ ⟨z,hz⟩
  let Z : Set X := I.subschemeι '' (((I.subschemeι ⁻¹ᵁ U₁ : I.subscheme.Opens) : Set I.subscheme)ᶜ)
  have hZ : Z.Finite := hfin.image _
  let : Finite Z := hZ.to_subtype
  obtain ⟨v₂,hv₂⟩ := exists_section_avoiding k s hs ((↑) : Z → X)
  refine ⟨![v₀,v₁,v₂], top_unique ?_⟩
  intro y hy
  apply Opens.mem_iSup.mpr
  by_cases hy₀ : y ∈ U₀
  · exact ⟨0,hy₀⟩
  by_cases hy₁ : y ∈ U₁
  · exact ⟨1,hy₁⟩
  have hyI : y ∈ I.support := by
    change y ∈ (I.support : Set X)
    rw [hsupport]
    exact hy₀
  obtain ⟨z,hz⟩ := (I.range_subschemeι ▸ hyI : y ∈ Set.range I.subschemeι)
  have hyZ : y ∈ Z := ⟨z, by change I.subschemeι z ∉ U₁; rwa [hz], hz⟩
  exact ⟨2,hv₂ ⟨y,hyZ⟩⟩

end
end MaximalSeshadri.Projective

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SurfaceProjection
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

theorem surface_finite_projection [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ t : Fin 3 → (O X ⟶ L.sheaf), ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
      IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨v,hv⟩ := surface_three_sections p L s hs
  let t : Fin 3 → (O X ⟶ L.sheaf) := fun i => sectionCombination k s (v i)
  have ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤ := hv
  refine ⟨t,ht,?_⟩
  let f := sectionsMorphism k t ht
  let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
    dsimp only [k]
    rw [toSpec_scalarMap]
    infer_instance
  let : IsProper f := sectionsMorphism_proper k t ht
  let : IsAffineHom f := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro y
    have hy : y ∈ ⨆ i : Fin 3, Proj.basicOpen (PolyGrade K (Fin 3)) (MvPolynomial.X i) := by
      rw [projective_coordinate_cover]
      trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hy
    refine ⟨Proj.basicOpen (PolyGrade K (Fin 3)) (MvPolynomial.X i),hi,
      Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide),?_⟩
    rw [show f = sectionsMorphism k t ht from rfl, sectionsMorphism_preimage]
    dsimp only [t]
    rw [← sectionsMorphism_hyperplane _ s hs]
    exact (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _
      (linearEquation_homogeneous (v i)) (by decide)).preimage _
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance,inferInstance⟩

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

theorem Surface.exists_finite_projection_s01_oai (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin 3 → (O S.scheme ⟶ (A.pow n).sheaf),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsFinite (sectionsMorphism (baseScalars S.structureMap) t ht) := by
  obtain ⟨n,hn,σ,hσ,s,hs,hclosed⟩ := S.ample_embedding A hA
  obtain ⟨t,ht,hf⟩ := @surface_finite_projection ℂ σ _ _ hσ S.scheme _ _
    S.structureMap _ _ (A.pow n) s hs hclosed
  exact ⟨n,hn,t,ht,hf⟩

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01_oai
