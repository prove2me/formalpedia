-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:18:59.845305+00:00
-- url     : https://prove2.me/submissions/d29e2ddb-bd1e-4da9-9ba2-ff209df46738

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_power_extension_ratio_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_local_powerSection_coefficient_s01
import Theorems.Thm_OAI_MaximalSeshadri_Projective_framedSectionsMorphism_closed_s01

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
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma toSpec_scalarMap (p : X ⟶ Spec (CommRingCat.of K)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) = p := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

lemma finiteType_coordinates {K R : Type u} [CommRing K] [CommRing R]
    (k : K →+* R) (hk : k.FiniteType) :
    ∃ n : ℕ, ∃ a : Fin n → R, Function.Surjective (eval₂Hom k a) := by
  let := k.toAlgebra
  have : Algebra.FiniteType K R := hk
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K R)
  refine ⟨n, fun i => f (X i), ?_⟩
  have heq : eval₂Hom k (fun i => f (X i)) = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (eval₂Hom_C _ _ _).trans (f.commutes c).symm
    · intro i
      exact eval₂Hom_X' _ _ _
  rw [heq]
  exact hf

theorem affine_coordinate_generators {K : Type u} [CommRing K] {X : Scheme.{u}}
    [IsAffine X] (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] :
    ∃ n : ℕ, ∃ a : Fin n → Γ(X, ⊤), Function.Surjective
      (eval₂Hom (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) a) := by
  have hp : p.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective
  exact finiteType_coordinates _ (hp.comp he)

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
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

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

lemma isIso_restricted_section {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : SectionOpens.isoOpen s = U) : IsIso (restrictSection U.ι s) := by
  subst U
  exact (sectionFrame s).isIso_inv

lemma coefficient_ratio {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ O U.toScheme) (s t : O X ⟶ M)
    (f : Γ(U.toScheme, ⊤)) (hs : coefficient e (restrictSection U.ι s) = 1)
    (ht : restrictSection U.ι t = scalarEnd f ≫ restrictSection U.ι s) :
    coefficient e (restrictSection U.ι t) = f := by
  rw [ht]
  change endValue (scalarEnd f ≫ restrictSection U.ι s ≫ e.hom) = f
  rw [endValue_comp, endValue_scalarEnd]
  change f * coefficient e (restrictSection U.ι s) = f
  rw [hs, mul_one]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme} {K ι : Type} [CommRing K] [Fintype ι]

theorem LineBundle.power_section_embedding_s01_oai [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] (L : LineBundle X)
    (s : ι → GlobalSections X L.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (sectionOpen X (s i)))
    (hne : ∀ i, (sectionOpen X (s i) : Set X).Nonempty) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U (i : ι) := sectionOpen X (s i)
  have hfinite (i : ι) : ∃ m : ℕ, ∃ b : Fin m → Γ((U i).toScheme, ⊤),
      Function.Surjective (eval₂Hom ((U i).ι.appTop.hom.comp k) b) := by
    let : IsAffine (U i).toScheme := haff i
    obtain ⟨m, b, hb⟩ := affine_coordinate_generators ((U i).ι ≫ p)
    refine ⟨m, b, ?_⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc, k] using hb
  choose m b hb using hfinite
  choose N hN using fun i j => L.power_extension_ratio_s01 (s i) (hne i) (b i j)
  let n := max 1 (Finset.univ.sup (fun v : (i : ι) × Fin (m i) => N v.1 v.2))
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hn' (i : ι) (j : Fin (m i)) : N i j ≤ n :=
    (Finset.le_sup (f := fun v : (i : ι) × Fin (m i) => N v.1 v.2)
      (Finset.mem_univ ⟨i, j⟩)).trans (le_max_right _ _)
  choose t ht using fun i j => hN i j n (hn' i j)
  let σ := ι ⊕ ((i : ι) × Fin (m i))
  let S : σ → GlobalSections X (modulePow X L.sheaf n) :=
    Sum.elim (fun i => powerSection (s i) n) (fun v => t v.1 v.2)
  have hU (i : ι) : SectionOpens.isoOpen (S (Sum.inl i)) = U i :=
    L.sectionOpen_power (s i) hn
  have hSn (i : ι) : IsIso (restrictSection (U i).ι (S (Sum.inl i))) :=
    isIso_restricted_section _ _ (hU i)
  let e (i : ι) : (modulePow X L.sheaf n).restrict (U i).ι ≅ O (U i).toScheme :=
    (asIso (restrictSection (U i).ι (S (Sum.inl i)))).symm
  have hnorm (i : ι) : coefficient (e i) (restrictSection (U i).ι (S (Sum.inl i))) = 1 :=
    coefficient_frame (e i)
  have hS : (⨆ v, SectionOpens.isoOpen (S v)) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact (le_of_eq (hU i).symm).trans (le_iSup (fun v : σ => SectionOpens.isoOpen (S v)) (Sum.inl i))
  have hproper : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
    rw [toSpec_scalarMap]
    infer_instance
  have hgen (i : ι) : Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun v => coefficient (e i) (restrictSection (U i).ι (S v)))) := by
    have heq : (fun v => coefficient (e i) (restrictSection (U i).ι (S v))) ∘
        (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) = b i := by
      funext j
      exact coefficient_ratio (e i) (S (Sum.inl i)) (S (Sum.inr ⟨i, j⟩)) (b i j)
        (hnorm i) (ht i j)
    intro r
    obtain ⟨q, hq⟩ := hb i r
    refine ⟨rename (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) q, ?_⟩
    rw [eval₂Hom_rename, heq]
    exact hq
  have hclosed := framedSectionsMorphism_closed_s01 k S U hc e Sum.inl hnorm hU
    (fun i => haff i) hgen
  rw [framedSectionsMorphism_eq_sectionsMorphism k S hS U hc e Sum.inl hnorm] at hclosed
  exact ⟨n, hn, σ, inferInstance, S, hS, hclosed⟩

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01_oai := @OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01_oai
