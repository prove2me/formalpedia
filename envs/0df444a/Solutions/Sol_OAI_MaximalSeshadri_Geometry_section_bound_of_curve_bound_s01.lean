-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:21:19.62429+00:00
-- url     : https://prove2.me/submissions/c33fcaed-fd1a-48a5-a2aa-2bbad1a0eb17

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_divide_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_invertible_ideal_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_residual_order_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_effective_mixed_nonneg_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_etale_line_frame_inside_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler_s01

section
-- module Solutions.Q223_SES.Seshadri_Configurations_AffinePointParameters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_factor {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (p : Over.mk (𝟙 complexBase) ⟶ Over.mk f)
    (hp : p.left (fieldPoint ℂ) ∈ U.1) :
    ∃ ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ,
      affineComplexPoint f U ρ = p := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hr : Set.range p.left ⊆ Set.range U.2.fromSpec := by
    rintro _ ⟨z,rfl⟩
    change Spec (CommRingCat.of ℂ) at z
    rw [show z = fieldPoint ℂ from Subsingleton.elim _ _,U.2.range_fromSpec]
    exact hp
  let l := IsOpenImmersion.lift U.2.fromSpec p.left hr
  let q := Spec.preimage l
  have hq : Spec.map q ≫ U.2.fromSpec = p.left := by
    rw [Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ hr
  have hg : CommRingCat.ofHom (openScalars f U.1) ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,← Category.assoc,hq,Spec.map_id]
    exact p.w
  let ρ : Γ(X,U.1) →ₐ[ℂ] ℂ :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hg c }
  refine ⟨ρ,?_⟩
  apply Over.OverMorphism.ext
  exact hq

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.section_coefficient_regular [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    IsRegular (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) := by
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  have he := (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective
  apply he
  change U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) =
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (0 : O X ⟶ L.sheaf)))
  exact h.trans (by rw [restrictSection_zero, coefficient_zero, map_zero])
end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_FramedPullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have leftSection : uF.inv ≫ F.map s =
        restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) := by
      dsimp only [uF, F, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫
          sectionMap) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
            (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s)).symm)
    have rightSection : uG.inv ≫ G.map s =
        pullbackSection (f ∣_ U) (restrictSection U.ι s) := by
      dsimp only [uG, G, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
          ((Scheme.Modules.pullback (f ∣_ U)).map_comp
            (Scheme.Modules.restrictUnitIso U.ι).inv
            ((Scheme.Modules.restrictFunctor U.ι).map s)).symm)
    exact (congrArg (coefficient eF) leftSection).symm.trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) rightSection))
  rw [he', coefficient_pullback]

end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_OpenChartDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

lemma chart_topIso_naturality (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma structuralOpenChartMap_apply (p : X ⟶ Spec (CommRingCat.of ℂ))
    (j : Y ⟶ X) (U : X.Opens) (f : Γ(X,U)) :
    letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
    structuralOpenChartMap p j U f = (j ⁻¹ᵁ U).topIso.inv (j.app U f) := by
  change (j ∣_ U).appTop (U.topIso.inv f) = _
  rw [← chart_topIso_naturality]
  simp only [CommRingCat.comp_apply]
  rw [U.topIso.inv_hom_id_apply]

lemma structuralOpenChartMap_ker (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) :
    letI : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
    letI : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
      (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
    RingHom.ker (structuralOpenChartMap p I.subschemeι U.1).toRingHom = I.ideal U := by
  ext t
  change structuralOpenChartMap p I.subschemeι U.1 t = 0 ↔ t ∈ I.ideal U
  rw [structuralOpenChartMap_apply, ← I.ker_subschemeι_app U]
  change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv (I.subschemeι.app U.1 t) = 0 ↔
    I.subschemeι.app U.1 t = 0
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeometricDivision
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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma pullback_zero_coefficient_mem (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hs : pullbackSection I.subschemeι s = 0) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ I.ideal U := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
  rw [← structuralOpenChartMap_ker p I U]
  change structuralOpenChartMap p I.subschemeι U.1
    (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) = 0
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame I.subschemeι U.1 e s
  have hzero : coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) = 0 := by
    rw [hs,restrictSection_zero,coefficient_zero]
  rw [he] at hzero
  change (I.subschemeι ∣_ U.1).appTop
    (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = 0
  rw [U.1.topIso.hom_inv_id_apply]
  exact hzero

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCoefficientOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma affineCoefficient_change {M : X.Modules} (U : X.affineOpens)
    (e f : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    Associated (affineCoefficient U e s) (affineCoefficient U f s) := by
  unfold affineCoefficient
  rw [coefficient_change e f, map_mul]
  exact associated_unit_mul_right _ _ ((frameChange e f).isUnit.map U.1.topIso.hom.hom)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.EtaleDimension
noncomputable section
open IsLocalRing

lemma local_unramified_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal R) (maximalIdeal S)
  rw [hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  have H : ((maximalIdeal S).height : WithBot ℕ∞) ≤ (maximalIdeal R).height := by exact_mod_cast h
  simpa only [maximalIdeal_height_eq_ringKrullDim] using H

lemma etale_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro q hq
  let := hq
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq := Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have H := local_unramified_dimension_le Rp Sq
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rp,
    IsLocalization.AtPrime.ringKrullDim_eq_height q Sq] at H
  exact H.trans ((ringKrullDim_le_iff_height_le _).mp le_rfl inferInstance)

lemma etale_surface_dimension_le (K S : Type*) [Field K] [CommRing S]
    [Algebra (MvPolynomial (Fin 2) K) S]
    [Algebra.Etale (MvPolynomial (Fin 2) K) S] : ringKrullDim S ≤ 2 := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 2) K) S
  have h := etale_dimension_le (MvPolynomial (Fin 2) K) S
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing] using h

end
end MaximalSeshadri.EtaleDimension
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleLowerDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.EtaleDimension
noncomputable section
open IsLocalRing

lemma polynomial_point_height (K : Type*) [Field K] (n : ℕ)
    (f : MvPolynomial (Fin n) K →ₐ[K] K) : (RingHom.ker f).height = n := by
  induction n with
  | zero =>
    have h := Ideal.height_le_ringKrullDim_of_ne_top (R := MvPolynomial (Fin 0) K)
      (RingHom.ker_ne_top f)
    simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      Nat.card_eq_fintype_card, Nat.cast_zero, zero_add] at h
    have hh : (RingHom.ker f).height ≤ 0 := by exact_mod_cast h
    simpa only [Nat.cast_zero] using le_antisymm hh (bot_le : 0 ≤ (RingHom.ker f).height)
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv K n
    let g : Polynomial (MvPolynomial (Fin n) K) →ₐ[K] K := f.comp e.symm.toAlgHom
    let h : MvPolynomial (Fin n) K →ₐ[K] K := g.comp (Polynomial.CAlgHom (R := K))
    let : (RingHom.ker g).IsMaximal := RingHom.ker_isMaximal_of_surjective g
      (fun k => ⟨algebraMap K _ k,g.commutes k⟩)
    let : (RingHom.ker g).LiesOver (RingHom.ker h) := ⟨by rfl⟩
    have H := Polynomial.height_eq_height_add_one (RingHom.ker h) (RingHom.ker g)
    have he : (RingHom.ker g).height = (RingHom.ker f).height :=
      e.symm.toRingEquiv.height_comap (RingHom.ker f)
    rw [he,ih h] at H
    simpa only [Nat.cast_add,Nat.cast_one] using H

lemma polynomial_point_height_finite (K ι : Type*) [Field K] [Fintype ι]
    (f : MvPolynomial ι K →ₐ[K] K) : (RingHom.ker f).height = Fintype.card ι := by
  let e := MvPolynomial.renameEquiv K (Fintype.equivFin ι)
  have h := polynomial_point_height K (Fintype.card ι) (f.comp e.symm.toAlgHom)
  have he : (RingHom.ker (f.comp e.symm.toAlgHom)).height = (RingHom.ker f).height :=
    e.symm.toRingEquiv.height_comap (RingHom.ker f)
  rwa [he] at h

theorem etale_principal_dimension_lower (K S ι : Type*) [Field K] [CommRing S]
    [Fintype ι] [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S] [Algebra.Etale (MvPolynomial ι K) S]
    (f : S →ₐ[K] K) (r : S) (hr : f r = 0) :
    (Fintype.card ι : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.span {r}) + 1 := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial ι K) S
  let g : MvPolynomial ι K →ₐ[K] S := IsScalarTower.toAlgHom K (MvPolynomial ι K) S
  let p := RingHom.ker (f.comp g)
  let P := RingHom.ker f
  let : p.IsPrime := RingHom.ker_isPrime (f.comp g)
  let : P.IsPrime := RingHom.ker_isPrime f
  let : P.LiesOver p := ⟨by rfl⟩
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hh : p.height ≤ P.height := H ▸ le_add_of_nonneg_right bot_le
  rw [show p.height = Fintype.card ι from polynomial_point_height_finite K ι (f.comp g)] at hh
  have hh' : (Fintype.card ι : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by exact_mod_cast hh
  exact hh'.trans (Ideal.height_le_ringKrullDim_quotient_add_one hr)

end
end MaximalSeshadri.EtaleDimension

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_IntegralImage
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {X Y : Scheme.{0}}

lemma integral_scheme_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  let (chart : f.ker.subschemeCover.openCover.I₀) :
      AlgebraicGeometry.IsReduced (f.ker.subschemeCover.openCover.X chart) := by
    change Y.affineOpens at chart
    let : _root_.IsReduced (Γ(Y,chart.1) ⧸ f.ker.ideal chart) := by
      rw [Scheme.Hom.ker_apply]
      exact isReduced_of_injective (RingHom.kerLift (f.app chart.1).hom)
        (RingHom.kerLift_injective (f.app chart.1).hom)
    change IsReduced (Spec (.of (Γ(Y,chart.1) ⧸ f.ker.ideal chart)))
    infer_instance
  let : IsReduced f.image := IsReduced.of_openCover f.image f.ker.subschemeCover.openCover
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image f.toImage
        f.toImage.continuous.continuousOn
  let : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

lemma residue_image_integral (X : Scheme.{0}) (x : X) :
    IsIntegral (X.fromSpecResidueField x).image := integral_scheme_image _

lemma residue_image_range (X : Scheme.{0}) (x : X) :
    Set.range (X.fromSpecResidueField x).imageι = closure {x} := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι,
    Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalDimension
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
open AlgebraicGeometry TopologicalSpace Order

lemma scheme_dimension_eq_point_dimension (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

lemma scheme_dimension_le_of_neighborhoods (X : Scheme) (d : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Scheme) (f : U ⟶ X), IsOpenImmersion f ∧
      x ∈ Set.range f ∧ topologicalKrullDim U ≤ d) : topologicalKrullDim X ≤ d := by
  rw [scheme_dimension_eq_point_dimension, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨U,f,hf,⟨y,rfl⟩,hd⟩ := h x
  let := hf
  rw [AlgebraicGeometry.coheight_eq_of_isOpenImmersion]
  exact (Order.coheight_le_krullDim y).trans ((scheme_dimension_eq_point_dimension U) ▸ hd)

lemma subscheme_dimension_le_of_affine_neighborhoods {X : Scheme}
    (I : X.IdealSheafData) (d : WithBot ℕ∞)
    (h : ∀ x : I.subscheme, ∃ U : X.affineOpens, I.subschemeι x ∈ U.1 ∧
      ringKrullDim (Γ(X,U.1) ⧸ I.ideal U) ≤ d) :
    topologicalKrullDim I.subscheme ≤ d := by
  apply scheme_dimension_le_of_neighborhoods
  intro x
  obtain ⟨U,hx,hd⟩ := h x
  let := I.subschemeCover.map_prop U
  refine ⟨_, I.subschemeCover.f U,inferInstance,?_,?_⟩
  · change x ∈ (I.subschemeCover.f U).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx
  · exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans hd

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PullbackSectionOpenExact
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f U e
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionComponent
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_zero_of_range (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (f : Y ⟶ X) [IsIntegral Y] (h : ∀ y, f y ∉ isoOpen s) :
    pullbackSection f s = 0 := by
  let pulledSection : O Y ⟶ (L.pullback f).sheaf := pullbackSection f s
  have htopen : isoOpen pulledSection = f ⁻¹ᵁ isoOpen s := pullback_isoOpen_eq L s f
  change pulledSection = 0
  by_contra hn
  apply (L.pullback f).isoOpen_ne_bot pulledSection hn
  rw [htopen]
  apply bot_unique
  intro y hy
  exact (h y hy).elim

lemma affineCoefficient_basicOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    X.basicOpen (affineCoefficient U e s) = U.1 ⊓ isoOpen s := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv]
  have he : U.1.topIso.inv (affineCoefficient U e s) =
      coefficient e (restrictSection U.1.ι s) := by
    exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id _
  rw [he,← preimage_isoOpen s U.1.ι e]
  ext x
  change (∃ q : U.1.toScheme, q.1 ∈ isoOpen s ∧ q.1 = x) ↔ _
  constructor
  · rintro ⟨q,hq,rfl⟩; exact ⟨q.property,hq⟩
  · rintro ⟨hx,hq⟩; exact ⟨⟨x,hx⟩,hq,rfl⟩

lemma Surface.annihilated_subscheme_dimension (S : Surface)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf) (hs : s ≠ 0)
    (I : S.scheme.IdealSheafData) (hi : pullbackSection I.subschemeι s = 0) :
    topologicalKrullDim I.subscheme ≤ 1 := by
  apply subscheme_dimension_le_of_affine_neighborhoods
  intro x
  obtain ⟨U,hx,-,e,t,het⟩ := S.etale_line_frame_inside_s01 L ⊤ (I.subschemeι x) (by trivial)
  let : Nonempty U.1 := ⟨⟨_,hx⟩⟩
  let φ := MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := het
  have hd := MaximalSeshadri.EtaleDimension.etale_surface_dimension_le ℂ Γ(S.scheme,U.1)
  let a := affineCoefficient U e s
  have ha : a ≠ 0 := (isRegular_iff_ne_zero).mp (L.section_coefficient_regular s hs U e)
  have ham : a ∈ I.ideal U := pullback_zero_coefficient_mem S.structureMap I L s hi U e
  refine ⟨U,hx,ENat.WithBot.add_le_add_one_right_iff.mp ?_⟩
  exact (ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (I.ideal U))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
      (Ideal.Quotient.eq_zero_iff_mem.mpr ham)).trans hd

lemma residue_image_one_le (X : Scheme.{0}) (x y : X) (hxy : x ⤳ y) (hne : x ≠ y) :
    1 ≤ topologicalKrullDim (X.fromSpecResidueField x).image := by
  let f := (X.fromSpecResidueField x).imageι
  have hx : x ∈ Set.range f := (residue_image_range X x).symm ▸ subset_closure (Set.mem_singleton x)
  have hy : y ∈ Set.range f := (residue_image_range X x).symm ▸ hxy.mem_closure
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  rw [scheme_dimension_eq_point_dimension,Order.one_le_krullDim_iff]
  refine ⟨b,a,lt_iff_le_not_ge.mpr ⟨?_,?_⟩⟩
  · apply Scheme.le_iff_specializes.mpr
    apply f.isEmbedding.isInducing.specializes_iff.mp
    rwa [ha,hb]
  · intro he
    apply hne
    have hba : y ⤳ x := by
      have H := (Scheme.le_iff_specializes.mp he).map f.continuous
      rwa [ha,hb] at H
    exact (hxy.antisymm hba).eq

theorem Surface.section_contains_curve (S : Surface) (L : LineBundle S.scheme)
    (s : O S.scheme ⟶ L.sheaf) (hs : s ≠ 0)
    (U : S.scheme.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra; Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (hρ : ρ (affineCoefficient U e s) = 0) :
    ∃ C : IntegralCurve S, pullbackSection C.embedding s = 0 := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  let φ := MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change openScalars S.structureMap U.1 z = φ (MvPolynomial.C z)
      simp [φ])
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := het
  let a := affineCoefficient U e s
  let J := Ideal.span {a}
  have hd := MaximalSeshadri.EtaleDimension.etale_principal_dimension_lower ℂ Γ(S.scheme,U.1)
    (Fin 2) ρ a hρ
  have hd' : 1 ≤ ringKrullDim (Γ(S.scheme,U.1) ⧸ J) := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [J]
  rw [ringKrullDim_quotient,Order.one_le_krullDim_iff] at hd'
  obtain ⟨x,y,hxy⟩ := hd'
  let z := U.2.fromSpec x.val
  let w := U.2.fromSpec y.val
  have hzw : z ⤳ w :=
    ((PrimeSpectrum.le_iff_specializes x.val y.val).mp hxy.le).map U.2.fromSpec.continuous
  have hne : z ≠ w := by
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hinj : Function.Injective U.2.fromSpec := U.2.fromSpec.isOpenEmbedding.injective
    intro h
    exact hxy.ne (Subtype.ext (hinj h))
  have hz : z ∉ isoOpen s := by
    intro h
    have hxU : z ∈ U.1 := by
      have H := Set.mem_range_self (f := U.2.fromSpec) x.val
      rwa [U.2.range_fromSpec] at H
    have H : z ∈ S.scheme.basicOpen a := by
      rw [affineCoefficient_basicOpen L s U e]; exact ⟨hxU,h⟩
    have H' : x.val ∈ PrimeSpectrum.basicOpen a := by
      rw [← U.2.fromSpec_preimage_basicOpen]
      exact H
    exact H' (x.property (Ideal.subset_span (Set.mem_singleton a)))
  let g := S.scheme.fromSpecResidueField z
  let := residue_image_integral S.scheme z
  have hzero : pullbackSection g.imageι s = 0 := by
    apply pullback_zero_of_range L s
    intro q
    have hq : g.imageι q ∈ closure {z} :=
      (residue_image_range S.scheme z) ▸ Set.mem_range_self q
    exact closure_minimal (Set.singleton_subset_iff.mpr hz) (isoOpen s).isOpen.isClosed_compl hq
  have hdim : topologicalKrullDim g.image = 1 := le_antisymm
    (S.annihilated_subscheme_dimension L s hs g.ker hzero)
    (residue_image_one_le S.scheme z w hzw hne)
  exact ⟨⟨g.image,g.imageι,inferInstance,inferInstance,hdim⟩,hzero⟩
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_CurveIdealDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem mixedEuler_tensor_right (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M N : LineBundle S.scheme) :
    mixedEuler S L (M.tensor N) = mixedEuler S L M + mixedEuler S L N := by
  classical
  obtain ⟨d,hd,-,n,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  have := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have h₁ := generated_curveDegree_eq_mixedEuler_s01 S L hL M d k s hs v hne hC
  have h₂ := generated_curveDegree_eq_mixedEuler_s01 S L hL N d k s hs v hne hC
  have h₃ := generated_curveDegree_eq_mixedEuler_s01 S L hL (M.tensor N) d k s hs v hne hC
  change curveDegree S M C = (d : ℤ)*mixedEuler S L M at h₁
  change curveDegree S N C = (d : ℤ)*mixedEuler S L N at h₂
  change curveDegree S (M.tensor N) C = (d : ℤ)*mixedEuler S L (M.tensor N) at h₃
  rw [curveDegree_tensor_s01 S L hL,h₁,h₂] at h₃
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply mul_left_cancel₀ hd'
  rw [← h₃]
  ring

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineOrderRestriction
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma affineCoefficient_restrict {M : X.Modules} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    affineCoefficient V (frameOnSmaller e V.1 h) s =
      X.presheaf.map (homOfLE h).op (affineCoefficient U e s) := by
  unfold affineCoefficient
  rw [frameOnSmaller_coefficient]
  change ((X.homOfLE h).appTop ≫ V.1.topIso.hom) _ =
    (U.1.topIso.hom ≫ X.presheaf.map (homOfLE h).op) _
  exact congrArg (fun restriction : Γ(U.1.toScheme, ⊤) ⟶ Γ(X, V.1) =>
    restriction (coefficient e (restrictSection U.1.ι s)))
    (X.restrictFunctorΓ.hom.naturality (homOfLE h).op)

lemma affine_point_germ_power (g : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ)
    (x : X) (hx : x ∈ U.1)
    (he : (affineComplexPoint g U ρ).left (fieldPoint ℂ) = x) (n : ℕ) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n).comap
      (X.presheaf.germ U.1 x hx).hom = (RingHom.ker ρ)^n := by
  let := (openScalars g U.1).toAlgebra
  let : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hp : RingHom.ker ρ = (U.2.primeIdealOf ⟨x,hx⟩).asIdeal := by
    change (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(X,U.1)).asIdeal = _
    apply congrArg PrimeSpectrum.asIdeal
    apply U.2.fromSpec.isOpenEmbedding.injective
    change (affineComplexPoint g U ρ).left (fieldPoint ℂ) =
      U.2.fromSpec (U.2.primeIdealOf ⟨x,hx⟩)
    exact he.trans (U.2.fromSpec_primeIdealOf ⟨x,hx⟩).symm
  let : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun z => ⟨algebraMap ℂ _ z,ρ.commutes z⟩)
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker ρ) := by
    change IsLocalization (RingHom.ker ρ).primeCompl _
    have hpc : (RingHom.ker ρ).primeCompl = (U.2.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl := by
      ext element; simp only [Ideal.mem_primeCompl_iff,hp]
    rw [hpc]
    exact U.2.isLocalization_stalk ⟨x,hx⟩
  exact IsLocalization.AtPrime.under_maximalIdeal_pow (RingHom.ker ρ) (X.presheaf.stalk x) n

lemma affineCoefficient_order_restrict_iff (g : X ⟶ complexBase)
    {M : X.Modules} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict V.1.ι ≅ O V.1.toScheme)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ)
    (σ : letI := (openScalars g V.1).toAlgebra; Γ(X,V.1) →ₐ[ℂ] ℂ)
    (he : affineComplexPoint g U ρ = affineComplexPoint g V σ)
    (s : O X ⟶ M) (n : ℕ) :
    affineCoefficient U e s ∈ (RingHom.ker ρ)^n ↔
      affineCoefficient V f s ∈ (RingHom.ker σ)^n := by
  let x := (affineComplexPoint g V σ).left (fieldPoint ℂ)
  have hx : x ∈ V.1 := by
    have H := Set.mem_range_self (f := V.2.fromSpec)
      (⟨RingHom.ker σ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(X,V.1))
    rw [V.2.range_fromSpec] at H
    exact H
  have hU := affine_point_germ_power g U ρ x (h hx)
    (congrArg (fun p => p.left (fieldPoint ℂ)) he) n
  have hV := affine_point_germ_power g V σ x hx rfl n
  have hass := affineCoefficient_change V (frameOnSmaller e V.1 h) f s
  rw [← Ideal.mem_iff_of_associated hass]
  rw [affineCoefficient_restrict,← hU,← hV]
  change (X.presheaf.germ U.1 x (h hx)) (affineCoefficient U e s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n ↔
    (X.presheaf.germ V.1 x hx)
      (X.presheaf.map (homOfLE h).op (affineCoefficient U e s)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n
  rw [TopCat.Presheaf.germ_res_apply]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCurveBound
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_mem (S : Surface) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∈ U.1 := by
  have H := Set.mem_range_self (f := U.2.fromSpec)
    (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
  rwa [U.2.range_fromSpec] at H

lemma Surface.section_contains_curve_of_order (S : Surface) (M : LineBundle S.scheme)
    (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : S.scheme.affineOpens) (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (n : ℕ) (hn : 0 < n)
    (ho : affineCoefficient U e s ∈ (RingHom.ker ρ)^n) :
    ∃ C : IntegralCurve S, pullbackSection C.embedding s = 0 := by
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  obtain ⟨V,hp,hVU,f,t,het⟩ := S.etale_line_frame_inside_s01 M U.1 p.image
    (affineComplexPoint_mem S U ρ)
  obtain ⟨σ,hσ⟩ := affineComplexPoint_factor S.structureMap V p hp
  have ho' := (affineCoefficient_order_restrict_iff S.structureMap U V hVU e f ρ σ
    hσ.symm s n).mp ho
  apply S.section_contains_curve M s hs V f t het σ
  exact (Ideal.pow_le_self (Nat.ne_of_gt hn)) ho'

theorem section_bound_of_curve_bound_s01_oai (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (p : Configuration S r) (a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ C : IntegralCurve S,
      a*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (M : LineBundle S.scheme) (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ)
    (hρ : ∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i)
    (n : Fin r → ℕ)
    (ho : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) :
    a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ) := by
  classical
  suffices H : ∀ d : ℕ, ∀ M : LineBundle S.scheme,
      (mixedEuler S L M).toNat = d →
      ∀ s : O S.scheme ⟶ M.sheaf, s ≠ 0 →
      ∀ U : Fin r → S.scheme.affineOpens,
      ∀ e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme,
      ∀ ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
        Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ,
      (∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i) →
      ∀ n : Fin r → ℕ,
      (∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) →
      a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ) from
    H _ M rfl s hs U e ρ hρ n ho
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro M hd s hs U e ρ hρ n ho
    have hnonneg := S.effective_mixed_nonneg_s01 L hL M s hs
    by_cases hz : ∀ i, n i = 0
    · simp only [hz,Finset.sum_const_zero,Nat.cast_zero,mul_zero]
      exact_mod_cast hnonneg
    obtain ⟨i,hi⟩ := not_forall.mp hz
    obtain ⟨C,hCs⟩ := S.section_contains_curve_of_order M s hs (U i) (e i) (ρ i)
      (n i) (Nat.pos_of_ne_zero hi) (ho i)
    obtain ⟨J,ι,hJ⟩ := C.invertible_ideal_s01 S
    obtain ⟨q,hq,-⟩ := C.divide_section_s01 S J M ι hJ s hCs
    have hq0 : q ≠ 0 := by
      intro hh
      apply hs
      rw [hh,zero_comp] at hq
      exact hq.symm
    have hqnonneg := S.effective_mixed_nonneg_s01 L hL (J.tensor M) q hq0
    have heq : mixedEuler S L (J.tensor M) = mixedEuler S L M-curveDegree S L C := by
      rw [mixedEuler_tensor_right S L hL,C.ideal_mixed_degree_s01 S L hL J ι hJ L]
      ring
    have hlt : (mixedEuler S L (J.tensor M)).toNat < d := by
      rw [← hd]
      have hpos := C.ample_degree_positive_s01 S L hL
      omega
    choose V f σ hσ horders using fun j => C.residual_order_s01 S J M ι hJ s q hq
      (U j) (e j) (ρ j) (n j) (ho j)
    have hb := ih _ hlt (J.tensor M) rfl q hq0 V f σ
      (fun j => (hσ j).trans (hρ j))
      (fun j => n j-curveMultiplicity S C (p.val j)) (by
        intro j
        simpa only [hρ j] using horders j)
    have hn : (∑ j, n j:ℕ) ≤ (∑ j, (n j-curveMultiplicity S C (p.val j)):ℕ)+
        totalMultiplicity S r C p := by
      unfold totalMultiplicity
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by omega
    have hn' : (∑ j, n j:ℕ) ≤
        ((∑ j, (n j-curveMultiplicity S C (p.val j)):ℕ):ℝ)+(totalMultiplicity S r C p:ℝ) := by
      exact_mod_cast hn
    have H := mul_le_mul_of_nonneg_left hn' ha
    have hc := hC C
    rw [heq,Int.cast_sub] at hb
    nlinarith only [H,hb,hc]

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01_oai := @OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01_oai
